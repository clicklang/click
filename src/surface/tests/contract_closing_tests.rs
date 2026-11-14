use super::*;

const C: &[(&str, &str)] = &[("closing.c", "int32 value(void) { return 7; }")];

fn proof(steps: &str) -> String {
    format!(
        r#"
        verifying "closing.c";
        int32 value() {{ ensures result == 7; }} by {{
            step_until(function.exit);
            {steps}
        }}
    "#
    )
}

#[test]
fn explicit_contract_closing_uses_ordinary_assumption_steps() {
    let source = proof("normalize(); assumption(); assumption(); assumption();");
    without_implicit_solve(|| verify_c0_sources(&source, C))
        .unwrap_or_else(|error| panic!("{}", error.message()));
}

#[test]
fn implicit_contract_closing_expands_into_explicit_steps() {
    let source = proof("solve();");
    verify_c0_sources(&source, C).unwrap();
    let expanded = expand_function_proof_source(&source, C, "value").unwrap();
    assert!(!expanded.contains("solve();"), "{expanded}");
    without_implicit_solve(|| verify_c0_sources(&expanded, C))
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

#[test]
fn per_clause_contract_closing_expands_after_its_source_proof() {
    let source = r#"verifying "closing.c";
        int32 value() { ensures result == 7 by { step_until(function.exit); }; }
    "#;
    let expanded = expand_c0_claim_source_by_label(source, C, "value.ensures_0").unwrap();
    without_implicit_solve(|| verify_c0_sources(&expanded, C))
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}
