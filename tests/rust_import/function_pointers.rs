use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/function-pointers/callback.click");

fn function_pointer_project() -> Project {
    let p = Project::from_fixture("design/charon-trial/function-pointers");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    p
}

#[test]
fn callable_signature_mismatch_displays_both_signatures() {
    let p = function_pointer_project();
    let prepared = p.prepared().unwrap();
    let mismatched = SIDECAR
        .replacen("f: fn(i32) -> i32", "f: fn(u32) -> u32", 1)
        .replacen("    requires Doubling(f);\n", "", 1);
    let error = C0VerificationSession::new_program_prepared(&mismatched, &prepared)
        .err()
        .expect("the callable signature mismatch must be refused");
    assert!(
        error
            .message()
            .contains(".click has uint32 (*)(uint32) f, C has int32 (*)(int32) f"),
        "{}",
        error.message()
    );
    assert!(
        !error.message().contains("FunctionPointer("),
        "{}",
        error.message()
    );
}

// `apply` calls through `f` under the contract it requires of `f`, `relay`
// forwards its own `f` to `apply`, and `caller` and `forward` pass `twice`,
// whose own contract meets that contract. Each piece is needed.
#[test]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn charon_calls_through_a_function_pointer_meet_its_named_contract() {
    let p = function_pointer_project();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    let twice = "fn function_pointers::twice(x: i32) -> i32 {\n    requires 0 <= x and x <= 1000;\n    ensures result == x + x;";
    let doubling = "contract fn Doubling(x: i32) -> i32 {\n    requires 0 <= x and x <= 1000;\n    ensures result == x + x;";
    // `relay` forwards `f` to `apply`, which requires the contract of it.
    let relay = "fn function_pointers::relay(f: fn(i32) -> i32, x: i32) -> i32 {\n    requires Doubling(f);\n";
    for (before, after, expected) in [
        (
            "    requires Doubling(f);\n",
            "",
            "call through function pointer",
        ),
        (
            relay,
            &relay.replace("    requires Doubling(f);\n", ""),
            "is missing prerequisite (precondition clause 1 of",
        ),
        (
            twice,
            &twice.replace("ensures result == x + x;", "ensures result >= 0;"),
            "does not satisfy named contract `Doubling`",
        ),
        (
            doubling,
            &doubling.replace("x + x;", "x + x + 1;"),
            "unclosed goal",
        ),
    ] {
        let invalid = SIDECAR.replace(before, after);
        assert_ne!(invalid, SIDECAR);
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .expect("a missing or unmet callback contract must fail");
        assert!(format!("{error:?}").contains(expected), "{error:?}");
    }
}

#[test]
#[ignore = "nightly: 3.7s in the parallel gate"]
fn charon_function_pointer_tools_recheck_expanded_certificates() {
    let p = function_pointer_project();
    for command in ["profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "__rust_q_I17_function_pointers_I5_apply.contract",
        "__rust_q_I17_function_pointers_I6_caller.contract",
        "__rust_q_I17_function_pointers_I5_relay.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
    }
    assert_cli(&p, &["verify"]);
}
