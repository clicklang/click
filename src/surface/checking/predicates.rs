use super::*;

pub(in crate::surface) fn unfold_predicates_in_proposition(
    spec_definitions: SpecDefinitions<'_>,
    selected_definitions: &[String],
    proposition: &Proposition,
    assumptions: &PureFactContext,
) -> Result<Proposition, String> {
    let mut active = BTreeSet::new();
    unfold_predicates_in_proposition_with_active(
        spec_definitions,
        selected_definitions,
        proposition,
        assumptions,
        &mut active,
    )
}

pub(in crate::surface) fn unfold_predicates_in_proposition_with_active(
    spec_definitions: SpecDefinitions<'_>,
    selected_definitions: &[String],
    proposition: &Proposition,
    assumptions: &PureFactContext,
    active: &mut BTreeSet<String>,
) -> Result<Proposition, String> {
    match proposition {
        Proposition::Predicate { name, arguments }
            if selected_definitions
                .iter()
                .any(|predicate| predicate_instance_name_matches(name, predicate)) =>
        {
            if !active.insert(name.clone()) {
                return Err(format!("recursive unfold of predicate `{name}`"));
            }
            let source_name = selected_definitions
                .iter()
                .find(|candidate| predicate_instance_name_matches(name, candidate))
                .expect("the predicate guard selected a source name");
            let definition = spec_definitions
                .predicates
                .get(source_name)
                .ok_or_else(|| {
                    format!(
                        "unknown predicate `{source_name}`{}",
                        crate::surface::validation::library_import_hint(source_name)
                    )
                })?;
            let definition = instantiate_lowered_predicate_definition(definition, arguments)?;
            let unfolded = instantiate_predicate_definition(
                &definition,
                arguments,
                assumptions,
                spec_definitions,
            )?;
            active.remove(name);
            Ok(unfolded)
        }
        Proposition::And(left, right) => Ok(Proposition::And(
            Box::new(unfold_predicates_in_proposition_with_active(
                spec_definitions,
                selected_definitions,
                left,
                assumptions,
                active,
            )?),
            Box::new(unfold_predicates_in_proposition_with_active(
                spec_definitions,
                selected_definitions,
                right,
                assumptions,
                active,
            )?),
        )),
        Proposition::Or(left, right) => Ok(Proposition::Or(
            Box::new(unfold_predicates_in_proposition_with_active(
                spec_definitions,
                selected_definitions,
                left,
                assumptions,
                active,
            )?),
            Box::new(unfold_predicates_in_proposition_with_active(
                spec_definitions,
                selected_definitions,
                right,
                assumptions,
                active,
            )?),
        )),
        Proposition::Not(body) => Ok(Proposition::Not(Box::new(
            unfold_predicates_in_proposition_with_active(
                spec_definitions,
                selected_definitions,
                body,
                assumptions,
                active,
            )?,
        ))),
        Proposition::Implies(left, right) => {
            let left = unfold_predicates_in_proposition_with_active(
                spec_definitions,
                selected_definitions,
                left,
                assumptions,
                active,
            )?;
            let right_assumptions = assumptions.clone().assume_proposition(left.clone());
            let right = unfold_predicates_in_proposition_with_active(
                spec_definitions,
                selected_definitions,
                right,
                &right_assumptions,
                active,
            )?;
            Ok(Proposition::Implies(Box::new(left), Box::new(right)))
        }
        Proposition::ForAll {
            var,
            sort,
            body,
            name,
        } => Ok(Proposition::ForAll {
            var: *var,
            sort: sort.clone(),
            name: name.clone(),
            body: Box::new(unfold_predicates_in_proposition_with_active(
                spec_definitions,
                selected_definitions,
                body,
                assumptions,
                active,
            )?),
        }),
        Proposition::Exists {
            name,
            var,
            sort,
            body,
        } => Ok(Proposition::Exists {
            name: name.clone(),
            var: *var,
            sort: sort.clone(),
            body: Box::new(unfold_predicates_in_proposition_with_active(
                spec_definitions,
                selected_definitions,
                body,
                assumptions,
                active,
            )?),
        }),
        _ => Ok(proposition.clone()),
    }
}

fn predicate_instance_name_matches(instance: &str, source: &str) -> bool {
    instance == source
        || instance
            .strip_prefix(source)
            .is_some_and(|suffix| suffix.starts_with("::<"))
}

fn instantiate_lowered_predicate_definition(
    definition: &PredicateDefinition,
    arguments: &[Term],
) -> Result<PredicateDefinition, String> {
    if definition.type_parameters().is_empty() {
        return Ok(definition.clone());
    }
    let mut argument_index = 1;
    let mut argument_types = Vec::new();
    for parameter in definition.parameters() {
        let actual = if parameter_is_click_array_ref(parameter) {
            argument_index += 2;
            Some(parameter.click_type().clone())
        } else {
            let actual = match arguments.get(argument_index) {
                Some(Term::ProgramValue(value)) => Some(ClickType::Program(
                    generics::interface_type_from_program_type(value.value().program_type()),
                )),
                Some(Term::Algebraic(value)) => {
                    Some(generics::click_type_from_algebraic_value_type(
                        &value.native_compat().algebraic_type.value_type(),
                    ))
                }
                _ => None,
            };
            argument_index += 1;
            actual
        };
        argument_types.push(actual);
    }
    let substitution = generics::infer_type_substitution(
        "predicate",
        definition.name(),
        definition.type_parameters(),
        definition
            .parameters()
            .iter()
            .map(|parameter| parameter.click_type().clone()),
        argument_types,
    )?;
    generics::instantiate_predicate(definition, &substitution)
}

pub(in crate::surface) fn instantiate_predicate_definition(
    definition: &PredicateDefinition,
    arguments: &[Term],
    assumptions: &PureFactContext,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Proposition, String> {
    let (state, values, array_refs) = decode_predicate_arguments(definition, arguments)?;
    // The body takes the route every proof-side proposition takes:
    // elaborated with the parameters bound to the decoded arguments and
    // lowered by the kernel at the decoded state.
    crate::surface::proof::lower_fixed_state_proposition_through_kernel(
        definition.body(),
        assumptions,
        ContractEnvironment::new(&values, &array_refs),
        FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
        spec_definitions,
    )
}

pub(in crate::surface) fn decode_predicate_arguments(
    definition: &PredicateDefinition,
    arguments: &[Term],
) -> Result<(ExecutionState, ProgramValueBindings, ClickArrayRefs), String> {
    let expanded_len = 1 + definition
        .parameters()
        .iter()
        .map(|parameter| {
            if parameter_is_click_array_ref(parameter) {
                2
            } else {
                1
            }
        })
        .sum::<usize>();

    if arguments.len() == expanded_len {
        let Some(Term::ExecutionState(state)) = arguments.first() else {
            return Err(format!(
                "predicate `{}` is missing its resource-state state",
                definition.name()
            ));
        };
        let mut values = ProgramValueBindings::new();
        let mut array_refs = BTreeMap::new();
        let mut default_memory = None;
        let mut index = 1;
        for parameter in definition.parameters() {
            if parameter_is_click_array_ref(parameter) {
                let Some(Term::Memory(memory)) = arguments.get(index) else {
                    return Err(format!(
                        "predicate `{}` argument `{}` is missing its array-ref memory",
                        definition.name(),
                        parameter.name()
                    ));
                };
                let Some(term_source_0 @ Term::ProgramValue(_)) = arguments.get(index + 1) else {
                    return Err(format!(
                        "predicate `{}` argument `{}` is missing its array-ref pointer",
                        definition.name(),
                        parameter.name()
                    ));
                };
                let (Some(ProgramValue::Pointer(pointer)),) =
                    (term_source_0.program_value_native(),)
                else {
                    return Err(format!(
                        "predicate `{}` argument `{}` is missing its array-ref pointer",
                        definition.name(),
                        parameter.name()
                    ));
                };
                default_memory.get_or_insert_with(|| memory.clone());
                let element_type = click_array_element_type(parameter.interface_type())
                    .ok_or_else(|| {
                        format!(
                            "predicate `{}` argument `{}` is not an array-ref parameter",
                            definition.name(),
                            parameter.name()
                        )
                    })?;
                values.insert(
                    parameter.name().to_string(),
                    ProgramValue::typed_pointer(
                        pointer.address().clone(),
                        element_type.pointer_to().unwrap(),
                    ),
                );
                array_refs.insert(
                    parameter.name().to_string(),
                    ClickArrayRef {
                        point: crate::kernel::ProgramPoint::of_memory(memory),
                        pointer: pointer.address().clone(),
                        element_type,
                    },
                );
                index += 2;
            } else {
                let Some(Term::ProgramValue(value)) = arguments.get(index) else {
                    return Err(format!(
                        "predicate `{}` argument `{}` did not lower to a C value",
                        definition.name(),
                        parameter.name()
                    ));
                };
                values.insert(parameter.name().to_string(), value.native_compat().clone());
                index += 1;
            }
        }
        return Ok((
            state
                .clone()
                .with_memory(default_memory.unwrap_or_default()),
            values,
            array_refs,
        ));
    }

    Err(format!(
        "predicate `{}` has malformed lowered argument count: expected {} expanded argument term(s), got {}",
        definition.name(),
        expanded_len,
        arguments.len()
    ))
}
