use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/capturing-closures/closure.click");

fn capturing_closure_project() -> Project {
    let p = Project::from_fixture("design/charon-trial/capturing-closures");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    p
}

// A capturing closure passed as `&dyn Fn` carries its own contract, fixed to
// the values it captured, and a callee requiring a parameterized contract of
// it is answered by refinement from that contract.
#[test]
#[ignore = "nightly: 4.2s in the parallel gate"]
fn charon_capturing_closures_meet_parameterized_contracts() {
    let p = capturing_closure_project();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    // The caller's facts about a captured value hold in the refinement: the
    // closure's bound on `k` is the caller's, not the contract's. `moved`
    // captures `k + 1`, whose bound the refinement's exact routes do not
    // derive from the caller's bound on `k`, so it is left unselected.
    let moved = "fn capturing_closures::moved(k: i32, x: i32) -> i32 {\n    requires 0 <= k and k <= 999;\n    requires 0 <= x and x <= 1000;\n    ensures result == x + k + 1;\n} by { execute(); simp(); }\n";
    assert!(SIDECAR.contains(moved));
    let without_bound = SIDECAR
        .replacen("    requires 0 <= amount and amount <= 1000;\n", "", 1)
        .replacen(moved, "", 1);
    assert_ne!(without_bound, SIDECAR);
    C0VerificationSession::new_program_prepared(&without_bound, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    for (before, after, expected) in [
        // A closure contract weaker than the one required.
        (
            "    ensures result == y + k;\n",
            "    ensures result >= y;\n",
            "is missing prerequisite (precondition clause 1 of `__rust_q_I18_capturing_closures_I5_shift`)",
        ),
        // A closure that requires more than the contract provides.
        (
            "    requires 0 <= y and y <= 1000;\n    requires 0 <= k",
            "    requires 0 <= y and y <= 10;\n    requires 0 <= k",
            "is missing prerequisite (precondition clause 1 of `__rust_q_I18_capturing_closures_I5_shift`)",
        ),
        // The callee fixes the contract's value to something else.
        (
            "requires Adds(f, { amount: k });",
            "requires Adds(f, { amount: x });",
            "failed for `__rust_q_I18_capturing_closures_I5_shift.ensures_0`",
        ),
        // A false closure contract.
        (
            "    ensures result == y + m;\n",
            "    ensures result == y + m + 1;\n",
            "moved_K0.ensures_0`",
        ),
        // A closure that captures nothing is its function.
        (
            "    ensures result == y + 1;\n} by { execute(); simp(); }\n\nfn capturing_closures::plain(",
            "    ensures result >= y;\n} by { execute(); simp(); }\n\nfn capturing_closures::plain(",
            "does not satisfy named contract `Increments`",
        ),
    ] {
        let invalid = SIDECAR.replacen(before, after, 1);
        assert_ne!(invalid, SIDECAR, "{before}");
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .expect("a closure without the contract its use needs must fail");
        let rendered = format!("{error:?} {error}");
        assert!(rendered.contains(expected), "{rendered}");
    }
}

#[test]
#[ignore = "nightly: 7.4s in the parallel gate"]
fn charon_capturing_closure_tools_recheck_expanded_certificates() {
    let p = capturing_closure_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "__rust_q_I18_capturing_closures_I6_caller_K0.contract",
        "__rust_q_I18_capturing_closures_I6_caller.contract",
        "__rust_q_I18_capturing_closures_I5_moved.contract",
        "__rust_q_I18_capturing_closures_I5_plain.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}
