use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/closures/closure.click");

fn closure_project() -> Project {
    let p = Project::from_fixture("design/charon-trial/closures");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    p
}

// A closure that captures nothing is verified under its rustc name,
// `caller::{closure#0}`, and a caller passing it for a `fn` pointer must
// show it meets the contract the callee requires of the pointer.
#[test]
#[ignore = "nightly: 1.6s in the parallel gate"]
fn charon_closures_passed_for_a_function_pointer_meet_its_named_contract() {
    let p = closure_project();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    let caller_closure = "fn closures::caller::{closure#0}(y: i32) -> i32 {\n    requires 0 <= y and y <= 1000;\n    ensures result == y + y;\n} by { execute(); simp(); }\n";
    assert!(SIDECAR.contains(caller_closure));
    for (before, after, expected) in [
        (
            caller_closure,
            caller_closure.replace("ensures result == y + y;", "ensures result >= 0;"),
            "does not satisfy named contract `Doubling`",
        ),
        (
            "    ensures result == z + z;",
            "    ensures result == z + z + 1;".to_string(),
            "failed for `__rust_q_I8_closures_I6_choose_K1.ensures_0`",
        ),
        (
            caller_closure,
            String::new(),
            "is missing prerequisite (precondition clause 1 of",
        ),
        (
            "fn closures::choose::{closure#1}(z: i32)",
            "fn closures::choose::{closure#2}(z: i32)".to_string(),
            "choose_K2` is not defined by any `verifying` source",
        ),
    ] {
        let invalid = SIDECAR.replace(before, &after);
        assert_ne!(invalid, SIDECAR);
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .expect("a closure without the contract its use needs must fail");
        let rendered = format!("{error:?} {error}");
        assert!(rendered.contains(expected), "{rendered}");
    }
}

#[test]
#[ignore = "nightly: 4.8s in the parallel gate"]
fn charon_closure_tools_recheck_expanded_certificates() {
    let p = closure_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "__rust_q_I8_closures_I6_caller_K0.contract",
        "__rust_q_I8_closures_I6_choose_K1.contract",
        "__rust_q_I8_closures_I6_choose.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}
