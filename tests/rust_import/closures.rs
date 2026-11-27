use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/closures/closure.click");

fn closure_project() -> Project {
    let p = Project::from_fixture("design/charon-trial/closures");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    p
}

// A closure that captures nothing is verified at its written expression,
// and a caller passing it for a `fn` pointer must
// show it meets the contract the callee requires of the pointer.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.6s in the parallel gate"]
fn charon_closures_passed_for_a_function_pointer_meet_its_named_contract() {
    let p = closure_project();
    let prepared = p.prepared().unwrap();
    ProgramVerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    let caller_closure = "fn closures::caller.statement(0).call(0).argument(0)(y: i32) -> i32 {\n    requires 0 <= y and y <= 1000;\n    ensures result == y + y;\n}\n";
    assert!(SIDECAR.contains(caller_closure));
    // Keep the original full positive check. Select complete function
    // proofs for local failures; declaration/interface boundary cases
    // retain their original whole-module checks.
    for (head, before, after, expected) in [
        (
            Some("fn closures::caller("),
            caller_closure,
            caller_closure.replace("ensures result == y + y;", "ensures result >= 0;"),
            "does not satisfy named contract `Doubling`",
        ),
        (
            Some("fn closures::choose.statement(0).statement(1).call(0).argument(0)("),
            "    ensures result == z + z;",
            "    ensures result == z + z + 1;".to_string(),
            "failed for `closures::choose.statement(0).statement(1).call(0).argument(0).ensures_0`",
        ),
        (
            Some("fn closures::caller("),
            caller_closure,
            String::new(),
            "requires an explicit prerequisite proof (precondition clause 1 of",
        ),
        (
            None,
            "fn closures::choose.statement(0).statement(1).call(0).argument(0)(z: i32)",
            "fn closures::choose.statement(0).statement(2).call(0).argument(0)(z: i32)".to_string(),
            "choose.statement(0).statement(2).call(0).argument(0)` is not defined by any `verifying` source",
        ),
    ] {
        let invalid = SIDECAR.replace(before, &after);
        assert_ne!(invalid, SIDECAR);
        let error = if let Some(head) = head {
            verify_rust_proof_after(&invalid, &prepared, head)
                .expect_err("a closure without the contract its use needs must fail")
        } else {
            ProgramVerificationSession::new_program_prepared(&invalid, &prepared)
                .err()
                .expect("a closure without the contract its use needs must fail")
        };
        let rendered = format!("{error:?} {error}");
        let rendered = click::languages::display_source_names(&rendered);
        assert!(rendered.contains(expected), "{rendered}");
    }
}

#[cfg(not(feature = "fast-gate"))]
#[test]
#[ignore = "nightly: 4.8s in the parallel gate"]
fn charon_closure_tools_recheck_expanded_certificates() {
    let p = closure_project();
    for command in ["profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "closures::caller.statement(0).call(0).argument(0).ensures_0",
        "closures::choose.statement(0).statement(1).call(0).argument(0).ensures_0",
        "__rust_q_I8_closures_I6_choose.ensures_0",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
    }
    assert_cli(&p, &["verify"]);
}
