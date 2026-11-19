use super::*;

const SIDECAR: &str = include_str!("../../design/charon-trial/extern-functions/ffi.click");

const INTERFACE: &str =
    include_str!("../../design/charon-trial/extern-functions/ffi.interface.click");

fn extern_function_project() -> Project {
    let p = Project::from_fixture("design/charon-trial/extern-functions");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    p
}

// `caller` calls `clamp_reading`, declared in an `unsafe extern "C"` block,
// under the imported interface contract: it must establish the
// precondition, may use only the postcondition, and the head must restate
// the declaration.
#[test]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn charon_extern_block_calls_meet_their_extern_contract() {
    let p = extern_function_project();
    let prepared = p.prepared().unwrap();
    let verify = |sidecar: &str, interface: &str| {
        let path = p.root.join("borrow.click");
        fs::write(p.root.join("ffi.interface.click"), interface).unwrap();
        let project = click::cli::read_click_project(&path, sidecar).unwrap();
        click::surface::verify_program_prepared_project(&project, &prepared)
    };
    verify(SIDECAR, INTERFACE).unwrap_or_else(|error| panic!("{error:?}"));

    // The imported Rust declaration is positional. The interface supplies
    // names for its contract, with the exact declared parameter types.
    let renamed = INTERFACE.replace("raw", "value");
    verify(SIDECAR, &renamed).unwrap_or_else(|error| panic!("{error:?}"));
    for (before, after, expected) in [
        ("    requires raw >= 0;\n", "", "precondition clause 1 of"),
        ("result <= 101;", "result <= 100;", "unclosed goal"),
    ] {
        let invalid = SIDECAR.replace(before, after);
        assert_ne!(invalid, SIDECAR);
        let error = verify(&invalid, INTERFACE).expect_err("the caller must satisfy its contract");
        assert!(format!("{error:?}").contains(expected), "{error:?}");
    }

    let invalid_interface = INTERFACE.replace("raw: i32", "raw: u32");
    let error = verify(SIDECAR, &invalid_interface)
        .expect_err("the interface must match the Rust declaration");
    assert!(
        format!("{error:?}")
            .contains("parameter 1 in `ffi.rs`: .click has UInt32 raw, C has Int32 raw"),
        "{error:?}"
    );

    let invalid = SIDECAR.replace("import \"ffi.interface.click\";", INTERFACE);
    let error = verify(&invalid, INTERFACE).expect_err("the Rust declaration has no body");
    assert!(
        format!("{error:?}").contains("is declared in an `extern` block and has no body to verify"),
        "{error:?}"
    );
}

#[cfg(not(feature = "fast-gate"))]
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
            "__rust_q_I16_extern_functions_I6_caller.ensures_0",
            "--in-place",
        ],
    );
    assert_cli(&p, &["verify"]);
}
