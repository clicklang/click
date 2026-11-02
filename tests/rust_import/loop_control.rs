use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/loop-control/control.click");

/// `break` from a `while` or `loop` body, `continue`, and a guard over a
/// narrow counter import as C loops; each exit runs its own path to the code
/// after the loop.
#[test]
fn charon_loop_control_verifies_break_and_continue() {
    let p = Project::from_fixture("design/charon-trial/loop-control");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    for (before, after, expected) in [
        // `scan` leaves at 3 through its `break`, not only at 0.
        (
            "fn scan(n: i32) -> i32 {\n    requires n >= 0;\n    ensures 0i32 <= result and result <= n;",
            "fn scan(n: i32) -> i32 {\n    requires n >= 0;\n    ensures result == 0i32;",
            "scan",
        ),
        // The `continue` path keeps `evens` unchanged, but only the
        // invariant says it stays below `i`.
        (
            "        invariant 0i32 <= i and i <= n and 0i32 <= evens and evens <= i;\n",
            "        invariant 0i32 <= i and i <= n and 0i32 <= evens;\n",
            "count_evens",
        ),
    ] {
        // The successful run above checks the entire fixture. Each mutation
        // only needs to recheck the function whose proof it invalidates.
        let function = SIDECAR
            .split("\nfn ")
            .skip(1)
            .find(|function| function.starts_with(&format!("{expected}(")))
            .map(|function| format!("fn {function}"))
            .unwrap_or_else(|| panic!("missing function `{expected}`"));
        assert!(function.contains(before), "{before}");
        let invalid = format!(
            "verifying \"control.rs\";\n{}",
            function.replacen(before, after, 1)
        );
        assert_proof_failure(&invalid, &prepared, expected);
    }

    // `break i` can return before `i` reaches `limit`. A concrete witness
    // exercises that exit without rechecking the general loop invariant and
    // searching for an impossible symbolic postcondition. Check its true
    // result first so an execution failure cannot pass the negative test.
    let witness = r#"verifying "control.rs";
fn first_stop(n: i32, limit: i32) -> i32 {
    requires n == 0i32 and limit == 1i32;
    ensures result == 0i32;
} by {
    step_until(function.exit);
}"#;
    C0VerificationSession::new_program_prepared(witness, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    let invalid = witness.replace("ensures result == 0i32;", "ensures result == limit;");
    assert_ne!(witness, invalid);
    assert_proof_failure(&invalid, &prepared, "first_stop");
}

fn assert_proof_failure(
    source: &str,
    prepared: &click::languages::rust::PreparedRustImport,
    function: &str,
) {
    let error = C0VerificationSession::new_program_prepared(source, prepared)
        .err()
        .unwrap_or_else(|| panic!("false claim in `{function}` must fail"));
    assert_eq!(
        error.kind(),
        click::surface::ClickErrorKind::Proof,
        "{function}: {error}"
    );
    let rendered = format!("{error:?} {error}");
    assert!(rendered.contains(function), "{function}: {rendered}");
}
