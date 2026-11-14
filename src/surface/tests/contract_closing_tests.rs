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
    without_implicit_solve(|| verify_c_sources(&source, C))
        .unwrap_or_else(|error| panic!("{}", error.message()));
}

#[test]
fn implicit_contract_closing_expands_into_explicit_steps() {
    let source = proof("solve();");
    verify_c_sources(&source, C).unwrap();
    let expanded = expand_function_proof_source(&source, C, "value").unwrap();
    assert!(!expanded.contains("solve();"), "{expanded}");
    without_implicit_solve(|| verify_c_sources(&expanded, C))
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

#[test]
fn per_clause_contract_closing_expands_after_its_source_proof() {
    let source = r#"verifying "closing.c";
        int32 value() { ensures result == 7 by { step_until(function.exit); }; }
    "#;
    let expanded = expand_c_claim_source_by_label(source, C, "value.ensures_0").unwrap();
    without_implicit_solve(|| verify_c_sources(&expanded, C))
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

#[test]
fn omitted_closing_steps_leave_their_obligations_open() {
    for (count, goal) in [
        (0, "joint returned resources"),
        (1, "allocation lifetime"),
        (2, "write footprint"),
    ] {
        let source = proof(&format!("normalize(); {}", "assumption(); ".repeat(count)));
        let error = without_implicit_solve(|| verify_c_sources(&source, C))
            .expect_err("packaging cannot supply an omitted proof");
        assert!(
            error
                .message()
                .contains(&format!("unproved {goal} obligation")),
            "{error}"
        );
        verify_c_sources(&source, C)
            .expect("the implicit solver supplies the same omitted operations");
    }
}

#[test]
fn written_solve_closes_only_one_selected_closing_goal() {
    let source = proof("normalize(); solve();");
    let error = without_implicit_solve(|| verify_c_sources(&source, C)).unwrap_err();
    assert!(
        error
            .message()
            .contains("unproved allocation lifetime obligation"),
        "{error}"
    );
}

#[test]
fn expansion_writes_each_closing_step_and_requires_them_when_cold() {
    let source = proof("normalize();");
    let expanded = expand_function_proof_source(&source, C, "value").unwrap();
    assert_eq!(expanded.matches("assumption();").count(), 3, "{expanded}");
    without_implicit_solve(|| verify_c_sources(&expanded, C)).unwrap();
    let last = expanded.rfind("assumption();").unwrap();
    let mut missing = expanded.clone();
    missing.replace_range(last..last + "assumption();".len(), "");
    let error = without_implicit_solve(|| verify_c_sources(&missing, C)).unwrap_err();
    assert!(
        error
            .message()
            .contains("unproved write footprint obligation"),
        "{error}"
    );
}

#[test]
fn proposition_closers_name_the_pending_closing_goal() {
    for closer in [
        "normalize();",
        "solve() using {};",
        "both { assumption(); } and { assumption(); }",
    ] {
        let source = proof(&format!("normalize(); {closer}"));
        let error = verify_c_sources(&source, C).unwrap_err();
        assert!(
            error.message().contains("requires a proposition goal"),
            "{error}"
        );
        assert!(
            error.message().contains("joint returned resources"),
            "{error}"
        );
        assert!(error.message().contains("assumption()"), "{error}");
    }
}

#[test]
fn footprint_refusal_names_the_goal_and_the_solver_that_failed() {
    let inputs = [(
        "writes.c",
        "int counter; int write(void) { counter = 9; return 0; }",
    )];
    for (steps, expected) in [
        (
            "normalize();",
            "the implicit solver could not prove the write footprint obligation",
        ),
        (
            "normalize(); assumption(); assumption(); assumption();",
            "this tactic could not prove the write footprint obligation",
        ),
    ] {
        let source = format!(
            r#"verifying "writes.c";
            int32 write() {{ ensures result == 0; }} by {{
                step_until(function.exit); {steps}
            }}"#
        );
        let error = verify_c_sources(&source, &inputs).unwrap_err();
        assert!(error.message().contains(expected), "{error}");
        assert!(
            error.message().contains("outside the mutable footprint"),
            "{error}"
        );
    }
}
