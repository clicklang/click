use super::*;

pub(super) fn resolve_code_region_ref(
    function_block: &FunctionBlock,
    region_ref: &CodeRegionRef,
    claim_label: &str,
    tactic_index: usize,
) -> Result<CodeRegion, ClickError> {
    region_ref
        .resolve(function_block.structural_clauses())
        .map_err(|error| match error {
            CodeRegionResolutionError::ExecutionTargetOnly(_) => ClickError::new(error.to_string()),
            CodeRegionResolutionError::UnknownLabel(_) => {
                ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {error}"))
            }
        })
}

pub(super) fn requirements_with_structural_unfolds(
    spec_definitions: SpecDefinitions<'_>,
    function_block: &FunctionBlock,
    requirement_pure_facts: &PureFactList,
) -> Result<PureFactList, String> {
    let unfolded_predicates = structural_unfold_tactic_names(function_block);
    let unfolded = unfold_available_predicate_facts(
        spec_definitions,
        &unfolded_predicates,
        requirement_pure_facts,
    )?;
    // Unfolding only appends, so the result extends the list and keeps the
    // context it carried.
    debug_assert!(unfolded.starts_with(requirement_pure_facts));
    let mut facts = requirement_pure_facts.clone();
    facts.extend(unfolded.into_iter().skip(requirement_pure_facts.len()));
    Ok(facts)
}

pub(super) fn structural_unfold_tactic_names(function_block: &FunctionBlock) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut names = Vec::new();
    for clause in function_block.structural_clauses() {
        for proof in [clause.initialize_proof(), clause.preserve_proof()]
            .into_iter()
            .flatten()
        {
            for name in proof.unfold_tactic_names() {
                if seen.insert(name.clone()) {
                    names.push(name);
                }
            }
        }
    }
    names
}
