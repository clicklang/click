use super::*;
use crate::kernel::ExecutionFactSource;

pub(in crate::surface::proof) struct CheckedFixedStateTheoremApplication {
    pub(in crate::surface::proof) facts: PureFactStore,
    pub(in crate::surface::proof) added_facts: Vec<Proposition>,
    /// All conclusions this application checked, including already-stated ones.
    pub(in crate::surface::proof) checked_facts: Vec<Proposition>,
}

/// Canonical checker for an explicit theorem application against one fixed
/// symbolic C state. Named premises are the complete evidence set. Ambient proof facts
/// and observable resource facts may only lower those premises and theorem
/// arguments; they cannot discharge an omitted theorem requirement.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn check_fixed_state_theorem_application_using_facts(
    theorem_environment: &TheoremEnvironment,
    application: &TheoremApplication,
    surface_premises: &[SyntaxProposition],
    claim_label: &str,
    tactic_index: usize,
    available: &PureFactStore,
    parameter_binding: ParameterBinding<'_>,
    fixed_state: FixedStateFrame<'_>,
    integer_values: &PersistentBinderMap<crate::kernel::SpecIntegerExpression>,
    algebraic_values: &BTreeMap<String, SpecAlgebraicExpression>,
    surface_propositions: &SurfacePropositionMap,
    effect_facts: &(impl ExecutionFactSource + ?Sized),
    spec_definitions: SpecDefinitions<'_>,
) -> Result<CheckedFixedStateTheoremApplication, ClickError> {
    let resource_facts = fixed_state
        .state
        .resources()
        .observable_facts_assuming_valid(available.assumptions());
    let mut lowering_assumptions = available.assumptions().clone();
    for fact in resource_facts {
        lowering_assumptions = lowering_assumptions.assume_proposition(fact);
    }

    if crate::surface::proof::theorem_application::preparing_application() {
        lowering_assumptions = lowering_assumptions.retaining_argument_obligations();
    }

    let mut explicit_premises = Vec::new();
    for surface_premise in surface_premises {
        let freshly_lowered = lower_fixed_state_proposition_with_integer_values(
            surface_premise,
            &lowering_assumptions,
            parameter_binding,
            fixed_state,
            integer_values,
            spec_definitions,
        );
        // Prefer the current-state lowering when it is checkable. A retained
        // surface form can also name an older raw load whose value the
        // current memory evaluates through (for example after swapping struct
        // fields); that historical kernel remains the fallback for premises
        // that cannot be checked under the current form.
        let recorded = || {
            surface_propositions
                .available_kernel_matching(surface_premise, |kernel| available.contains(kernel))
                .cloned()
        };
        let premise = match freshly_lowered {
            Ok(fresh) if available.available_across_effects(&fresh, &[]) => fresh,
            Ok(fresh) => recorded().unwrap_or(fresh),
            Err(message) => recorded().ok_or_else(|| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower `apply using` premise: {message}"
                ))
            })?,
        };
        // A true ground premise needs no ambient fact. The availability check
        // below evaluates retained literal comparisons by the rule every
        // `using` list shares
        // (`listed_premise_holds`), which also accepts an equality listed in
        // the other orientation from the fact held.
        if !available.listed_premise_available(&premise, &[], true) {
            let available_facts = available.to_vec();
            // Name the listed premise in the reader's own spelling: a
            // premise lowered to a constant or to an internal term says
            // neither which `using` entry was refused nor why.
            let constant_note = match &premise {
                condition_source_0 @ Proposition::ConditionIs(_, _)
                    if let Some((ConditionTerm::Constant(_), _)) =
                        condition_source_0.condition_native() =>
                {
                    " (it is false at this instance)"
                }
                condition_source_0 @ Proposition::ConditionIs(_, expected)
                    if let Some((
                        condition @ ConditionTerm::Compare {
                            format,
                            left,
                            right,
                            ..
                        },
                        _,
                    )) = condition_source_0.condition_native()
                        && (format.constant_from_term(left).is_some()
                            && format.constant_from_term(right).is_some()
                            && PureFactContext::new().decide(condition) == Some(!expected)) =>
                {
                    " (it is false at this instance)"
                }
                _ => "",
            };
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `apply using` requires an exact premise: listed premise `{}`{constant_note} is not an available fact: {}",
                crate::surface::diagnostics::describe_click_proposition(surface_premise),
                describe_missing_pure_fact(
                    &premise,
                    &available_facts,
                    fixed_state.state.resources().facts(),
                    parameter_binding,
                    effect_facts,
                )
            )));
        }
        // Citing a stated range cites both of its halves; see
        // `cite_range_span_guards`.
        crate::surface::proof::theorem_application::cite_range_span_guards(
            &premise,
            &mut explicit_premises,
            |guard| available.available_across_effects(guard, &[]),
        );
        if !explicit_premises.contains(&premise) {
            explicit_premises.push(premise);
        }
    }

    // The application reads the caller's environment only through its
    // arguments, so it needs only the names they mention.
    let mut names = BTreeSet::new();
    for argument in &application.arguments {
        crate::surface::lowering::collect_contract_expression_referenced_names(
            argument, &mut names,
        );
    }
    let (values, array_refs) =
        contract_environment_for_names(parameter_binding, &names, fixed_state.state).map_err(
            |error| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: {}",
                    error.message
                ))
            },
        )?;
    let native_result = fixed_state.native_result();
    let application_context = TheoremApplicationContext {
        parameters: parameter_binding,
        values: &values,
        array_refs: &array_refs,
        algebraic_values,
        pre_state: fixed_state.pre_state,
        post_state: fixed_state.state,
        result: native_result.as_deref(),
        recorded_states: fixed_state.recorded_states,
        integer_values,
        pointer_element_widths: parameter_pointer_element_widths_named(parameter_binding, &names),
    };
    let conclusions = instantiate_theorem_application_with_assumptions(
        theorem_environment,
        application,
        claim_label,
        None,
        tactic_index,
        &explicit_premises,
        &lowering_assumptions,
        &application_context,
        spec_definitions,
    )?;

    let mut facts = available.clone();
    let mut added_facts = Vec::new();
    for conclusion in &conclusions {
        if !facts.contains_top_level(conclusion) {
            added_facts.push(conclusion.clone());
        }
        facts = facts.with_kernel_checked_fact(conclusion.clone());
    }

    Ok(CheckedFixedStateTheoremApplication {
        facts,
        added_facts,
        checked_facts: conclusions,
    })
}
