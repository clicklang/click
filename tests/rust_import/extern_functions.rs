use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/extern-functions/ffi.click");

fn extern_function_project() -> Project {
    let p = Project::from_fixture("design/charon-trial/extern-functions");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    p
}

// `caller` calls `clamp_reading`, declared in an `unsafe extern "C"` block,
// under the sidecar's trusted `extern fn` contract: it must establish the
// precondition, may use only the postcondition, and the head must restate
// the declaration.
#[test]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn charon_extern_block_calls_meet_their_extern_contract() {
    let p = extern_function_project();
    let prepared = p.prepared().unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    let head = "extern fn extern_functions::clamp_reading(raw: i32) -> i32 {";
    // A head names the parameters; the declaration in the import has none.
    let renamed = SIDECAR
        .replace(
            head,
            "extern fn extern_functions::clamp_reading(value: i32) -> i32 {",
        )
        .replace(
            "    requires raw >= 0;\n    ensures 0",
            "    requires value >= 0;\n    ensures 0",
        );
    C0VerificationSession::new_program_prepared(&renamed, &prepared)
        .unwrap_or_else(|error| panic!("{error:?}"));
    let caller_requires = "    requires raw >= 0;\n    ensures 1";
    for (before, after, expected) in [
        (
            caller_requires,
            "    ensures 1",
            "is missing prerequisite (precondition clause 1 of",
        ),
        ("result <= 101;", "result <= 100;", "unclosed goal"),
        (
            head,
            "extern fn extern_functions::clamp_reading(raw: u32) -> i32 {",
            "parameter 1 in `ffi.rs`: .click has UInt32 raw, C has Int32 raw",
        ),
        (
            head,
            "fn extern_functions::clamp_reading(raw: i32) -> i32 {",
            "is declared in an `extern` block and has no body to verify",
        ),
    ] {
        let invalid = SIDECAR.replace(before, after);
        assert_ne!(invalid, SIDECAR);
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .expect("an unmet or misstated extern contract must fail");
        assert!(format!("{error:?}").contains(expected), "{error:?}");
    }
}

#[test]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn charon_extern_function_tools_recheck_expanded_certificates() {
    let p = extern_function_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    assert_cli(
        &p,
        &[
            "expand",
            "--claim",
            "__rust_q_I16_extern_functions_I6_caller.contract",
            "--in-place",
        ],
    );
    assert_cli(&p, &["verify"]);
}
