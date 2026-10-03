use super::*;

const SOURCE: &str = include_str!("../../design/charon-trial/array-values/bounds.rs");
const SIDECAR: &str = include_str!("../../design/charon-trial/array-values/bounds.click");
fn project() -> Project {
    let p = Project::new("");
    for (name, bytes) in [
        ("bounds.rs", SOURCE.as_bytes()),
        ("borrow.click", SIDECAR.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../../design/charon-trial/array-values/bounds.click.import.json")
                .as_slice(),
        ),
        (
            "bounds.ullbc",
            include_bytes!("../../design/charon-trial/array-values/bounds.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!("../../design/charon-trial/array-values/bounds.click.import.json.lock")
                .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}

#[test]
fn charon_array_reference_assignments_check_values_and_independent_snapshots() {
    let p = project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared).unwrap();
    for (before, after) in [
        ("ensures result == 5u32;", "ensures result == 3u32;"),
        ("ensures result == -3;", "ensures result == 7;"),
        ("ensures result == 7u32;", "ensures result == 9u32;"),
        ("ensures result == 0u64;", "ensures result == 1u64;"),
    ] {
        let invalid = SIDECAR.replace(before, after);
        assert_ne!(invalid, SIDECAR);
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}

#[test]
fn charon_array_reference_assignments_tools_recheck_expanded_certificates() {
    let p = project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "swap.contract",
        "self_copy.contract",
        "copy_million.contract",
        "fill_million.contract",
        "empty.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

#[test]
fn charon_array_values_unchanged_fixture_verifies_external_snapshots() {
    let p = Project::new("");
    let source = include_str!("../../design/charon-trial/array-values/arrays.rs");
    let sidecar = include_str!("../../design/charon-trial/array-values/arrays.click");
    assert_eq!(
        source,
        include_str!("../../examples/rust-array-values/arrays.rs")
    );
    assert_eq!(
        sidecar,
        include_str!("../../examples/rust-array-values/arrays.click")
    );
    for (name, bytes) in [
        ("arrays.rs", source.as_bytes()),
        ("borrow.click", sidecar.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../../design/charon-trial/array-values/arrays.click.import.json")
                .as_slice(),
        ),
        (
            "arrays.ullbc",
            include_bytes!("../../design/charon-trial/array-values/arrays.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!("../../design/charon-trial/array-values/arrays.click.import.json.lock")
                .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    for (before, after) in [
        ("ensures result == words[0];", "ensures result == words[1];"),
        (
            "ensures target[1] == old(source[1]);",
            "ensures target[1] == old(source[0]);",
        ),
        ("ensures *value == 5u32;", "ensures *value == 4u32;"),
    ] {
        let invalid = sidecar.replace(before, after);
        assert_ne!(invalid, sidecar);
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "copy_reference.contract",
        "copy_into.contract",
        "repeat_call.contract",
        "zero_repeat_call.contract",
        "argument_order.contract",
        "assignment_order.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

#[test]
#[ignore = "requires the pinned live Charon/compiler; scripts/check.sh --charon-live"]
fn charon_array_reference_assignments_live_refresh_and_borrow_rejections() {
    let p = project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &load_import(&p.config()).unwrap())
        .unwrap();
    for (source, diagnostic) in [
        ("pub fn bad(x: &[u32;2]) { *x = [1,2]; }", "E0594"),
        (
            "pub fn bad(x: &mut [u32;2]) { let y=&mut *x; *x=[1,2]; y[0]=3; }",
            "E0506",
        ),
        (
            "pub fn bad(x: [u32;2])->u32 { x[0] }",
            "by-value Rust arrays as parameters",
        ),
        (
            "pub fn bad()->[u32;2] { [1,2] }",
            "reference/aggregate returns",
        ),
    ] {
        fs::remove_file(p.root.join("bounds.ullbc")).unwrap();
        fs::write(p.root.join("bounds.rs"), source).unwrap();
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!p.root.join("bounds.ullbc").exists());
        fs::write(p.root.join("bounds.rs"), SOURCE).unwrap();
        refresh_import(&p.config()).unwrap();
    }
}

fn external_project() -> Project {
    let p = Project::new("");
    for (name, bytes) in [
        (
            "external.rs",
            include_bytes!("../../design/charon-trial/array-values/external.rs").as_slice(),
        ),
        (
            "borrow.click",
            include_bytes!("../../design/charon-trial/array-values/external.click").as_slice(),
        ),
        (
            "borrow.click.import.json",
            include_bytes!("../../design/charon-trial/array-values/external.click.import.json")
                .as_slice(),
        ),
        (
            "external.ullbc",
            include_bytes!("../../design/charon-trial/array-values/external.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!(
                "../../design/charon-trial/array-values/external.click.import.json.lock"
            )
            .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}

#[test]
fn charon_external_array_copies_and_fills_verify_and_reject_false_bytes() {
    let p = external_project();
    let sidecar = fs::read_to_string(p.root.join("borrow.click")).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    for (before, after) in [
        ("old(source[0])", "old(source[1])"),
        ("target[999999] == value", "target[999999] == value + 1u32"),
        ("result == old(source[0])", "result == source[0]"),
    ] {
        let invalid = sidecar.replace(before, after);
        assert_ne!(invalid, sidecar);
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "copy_million.contract",
        "fill_million.contract",
        "independent.contract",
        "empty.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

#[test]
#[ignore = "requires the pinned live Charon/compiler; scripts/check.sh --charon-live"]
fn charon_external_array_copies_live_refresh() {
    let p = external_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(
        &fs::read_to_string(p.root.join("borrow.click")).unwrap(),
        &load_import(&p.config()).unwrap(),
    )
    .unwrap();
}
