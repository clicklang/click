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
fn explicit_contract_closing_uses_ordinary_known_steps() {
    let source = proof("normalize(); known(); known(); known();");
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
        let source = proof(&format!("normalize(); {}", "known(); ".repeat(count)));
        let error = without_implicit_solve(|| verify_c_sources(&source, C))
            .expect_err("ordinary completion cannot supply an omitted proof");
        assert!(
            error
                .message()
                .contains(&format!("outcome still owes contract closing: {goal}")),
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
            .contains("outcome still owes contract closing: allocation lifetime"),
        "{error}"
    );
}

#[test]
fn expansion_writes_each_closing_step_and_requires_them_when_cold() {
    let source = proof("normalize();");
    let expanded = expand_function_proof_source(&source, C, "value").unwrap();
    assert_eq!(expanded.matches("known();").count(), 3, "{expanded}");
    without_implicit_solve(|| verify_c_sources(&expanded, C)).unwrap();
    let last = expanded.rfind("known();").unwrap();
    let mut missing = expanded.clone();
    missing.replace_range(last..last + "known();".len(), "");
    let error = without_implicit_solve(|| verify_c_sources(&missing, C)).unwrap_err();
    assert!(
        error
            .message()
            .contains("outcome still owes contract closing: write footprint"),
        "{error}"
    );
}

#[test]
fn proposition_closers_name_the_pending_closing_goal() {
    for closer in [
        "normalize();",
        "solve() using {};",
        "both { known(); } and { known(); }",
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
        assert!(error.message().contains("known()"), "{error}");
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
            "normalize(); known(); known(); known();",
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

fn source_only_clauses(grouped: bool, last_value: i32) -> String {
    let clauses = format!(
        r#"
        ensures result == at(first, x) + 1{};
        ensures at(first, x) == {last_value}{};
    "#,
        if grouped {
            ""
        } else {
            " by { step(); mark first; }"
        },
        if grouped {
            ""
        } else {
            " by { step(); mark first; }"
        }
    );
    format!(
        r#"verifying "source_cells.c";
        int32 set_twice(int32 x) {{ {clauses} }} {}
    "#,
        if grouped {
            "by { step(); mark first; }"
        } else {
            ""
        }
    )
}

const SOURCE_CELLS_C: &[(&str, &str)] = &[(
    "source_cells.c",
    "int32 set_twice(int32 x) { x = 1; x = 2; return x; }",
)];

#[test]
fn grouped_source_only_claims_complete_and_expand_as_ordinary_proofs() {
    let source = source_only_clauses(true, 1);
    verify_c_sources(&source, SOURCE_CELLS_C).unwrap();
    let expanded = expand_function_proof_source(&source, SOURCE_CELLS_C, "set_twice").unwrap();
    without_implicit_solve(|| verify_c_sources(&expanded, SOURCE_CELLS_C))
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

#[test]
fn separate_source_only_clauses_complete_their_own_cells() {
    verify_c_sources(&source_only_clauses(false, 1), SOURCE_CELLS_C).unwrap();
}

#[test]
fn proving_one_source_only_clause_cannot_cover_a_false_sibling() {
    for grouped in [false, true] {
        assert!(verify_c_sources(&source_only_clauses(grouped, 9), SOURCE_CELLS_C).is_err());
    }
}
