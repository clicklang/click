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
            CodeRegionResolutionError::ExecutionTargetOnly(_)
            | CodeRegionResolutionError::StatementRegionTarget => {
                ClickError::new(error.to_string())
            }
            CodeRegionResolutionError::UnknownLabel(_) => {
                ClickError::new(format!("`{claim_label}` tactic {tactic_index}: {error}"))
            }
        })
}
