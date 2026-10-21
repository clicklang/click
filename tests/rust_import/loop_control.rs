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
        // `break i` returns the counter as the test found it.
        (
            "    ensures 0i32 <= result and result <= limit and result <= n;\n",
            "    ensures result == limit;\n",
            "first_stop",
        ),
    ] {
        assert!(SIDECAR.contains(before), "{before}");
        let invalid = SIDECAR.replacen(before, after, 1);
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .unwrap_or_else(|| panic!("`{before}` -> `{after}` must fail"));
        let rendered = format!("{error:?} {error}");
        assert!(rendered.contains(expected), "{expected}: {rendered}");
    }
}
