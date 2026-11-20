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
    let witness = r#"fn count_evens(n: i32) -> i32 {
    requires n == 4i32;
    ensures result == 2i32;
} by {
    step_until(function.exit);
}"#;
    let gate = with_rust_fixture_contract(SIDECAR, "count_evens", witness);
    ProgramVerificationSession::new_program_prepared(&gate, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    // `scan` can leave through its break at 3.
    let before = "fn scan(n: i32) -> i32 {\n    requires n >= 0;\n    ensures 0i32 <= result and result <= n;";
    let after = "fn scan(n: i32) -> i32 {\n    requires n >= 0;\n    ensures result == 0i32;";
    assert!(SIDECAR.contains(before), "{before}");
    assert_proof_failure(&SIDECAR.replacen(before, after, 1), &prepared, "scan");

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
    ProgramVerificationSession::new_program_prepared(witness, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    let invalid = witness.replace("ensures result == 0i32;", "ensures result == limit;");
    assert_ne!(witness, invalid);
    assert_proof_failure(&invalid, &prepared, "first_stop");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: symbolic continue proof took 4.8s in the focused gate profile"]
fn charon_continue_loop_verifies_symbolically() {
    let p = Project::from_fixture("design/charon-trial/loop-control");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    let prepared = p.prepared().unwrap();
    verify_rust_function(SIDECAR, &prepared, "count_evens")
        .unwrap_or_else(|error| panic!("{error:?}"));

    // The `continue` path needs the invariant to keep `evens` below `i`.
    let before = "        invariant 0i32 <= i and i <= n and 0i32 <= evens and evens <= i;\n";
    let after = "        invariant 0i32 <= i and i <= n and 0i32 <= evens;\n";
    assert!(SIDECAR.contains(before), "{before}");
    assert_proof_failure(
        &SIDECAR.replacen(before, after, 1),
        &prepared,
        "count_evens",
    );
}

fn assert_proof_failure(
    source: &str,
    prepared: &click::languages::rust::PreparedRustImport,
    function: &str,
) {
    let error =
        verify_rust_function(source, prepared, function).expect_err("false claim must fail");
    assert_eq!(
        error.kind(),
        click::surface::ClickErrorKind::Proof,
        "{function}: {error}"
    );
    let rendered = format!("{error:?} {error}");
    assert!(rendered.contains(function), "{function}: {rendered}");
}
