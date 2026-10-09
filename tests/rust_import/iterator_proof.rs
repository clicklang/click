use super::*;

fn project(fixture: &str) -> Project {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("design/charon-trial/iterator-proof")
        .join(fixture);
    let p = Project::new("");
    for (destination, original) in [
        ("sum.rs", "sum.rs"),
        ("sum.ullbc", "sum.ullbc"),
        ("borrow.click", "sum.click"),
        ("borrow.click.import.json", "sum.click.import.json"),
        (
            "borrow.click.import.json.lock",
            "sum.click.import.json.lock",
        ),
    ] {
        fs::write(
            p.root.join(destination),
            fs::read(root.join(original)).unwrap(),
        )
        .unwrap();
    }
    p
}
fn preserves_source_and_checks_obligations(fixture: &str) {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let migrated = root
        .join("design/charon-trial/iterator-proof")
        .join(fixture);
    let original = root.join("examples").join(fixture);
    assert_eq!(
        fs::read(migrated.join("sum.rs")).unwrap(),
        fs::read(original.join("sum.rs")).unwrap()
    );
    assert_eq!(
        fs::read(migrated.join("sum.click")).unwrap(),
        fs::read(original.join("sum.click")).unwrap()
    );
    let p = project(fixture);
    let prepared = load_import(&p.config()).unwrap();
    let proof = fs::read_to_string(p.root.join("borrow.click")).unwrap();
    assert!(!proof.contains("__rust_"));
    assert!(!proof.contains("statement("));
    C0VerificationSession::new_program_prepared(&proof, &prepared).unwrap();
    for invalid in [
        proof.replacen("views bytes[0..bytes.len()];", "", 1),
        proof.replacen(
            "ensures to_integer(result) == old(prefix(bytes, (int32)(uint32)bytes.len()));",
            "ensures to_integer(result) == old(prefix(bytes, (int32)(uint32)bytes.len())) + 1;",
            1,
        ),
        proof.replace("decreases iter_remaining;", "decreases -iter_remaining;"),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}
fn profile_agrees(fixture: &str) {
    let p = project(fixture);
    assert_cli(&p, &["verify"]);
    assert_cli(&p, &["profile"]);
}
fn expansion_rechecks(fixture: &str) {
    let p = project(fixture);
    assert_cli(&p, &["verify"]);
    assert_cli(&p, &["expand", "--claim", "sum.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}
fn audits_checked_frontiers(fixture: &str) {
    for selector in [
        "execute_until(read(0))",
        "execute_until(assignment(total, 1))",
        "execute_until(back_edge())",
    ] {
        let p = project(fixture);
        assert_cli(&p, &["verify"]);
        let proof = fs::read_to_string(p.root.join("borrow.click")).unwrap();
        let offset = proof.find(selector).unwrap();
        let line = proof[..offset].bytes().filter(|&b| b == b'\n').count() + 1;
        let column = offset - proof[..offset].rfind('\n').map_or(0, |p| p + 1) + 1;
        let cursor = format!("{}:{line}:{column}", p.root.join("borrow.click").display());
        assert_cli(&p, &["audit", "--start-at", &cursor, "--max-sites", "1"]);
    }
}

macro_rules! iterator_checks {
    ($fixture:literal, $obligations:ident, $profile:ident, $expand:ident, $audit:ident) => {
        #[test]
        fn $obligations() {
            preserves_source_and_checks_obligations($fixture);
        }
        #[test]
        #[ignore = "nightly: whole-example proof-tool rechecks"]
        fn $profile() {
            profile_agrees($fixture);
        }
        #[test]
        #[ignore = "nightly: whole-example proof-tool rechecks"]
        fn $expand() {
            expansion_rechecks($fixture);
        }
        #[test]
        #[ignore = "nightly: whole-example proof-tool rechecks"]
        fn $audit() {
            audits_checked_frontiers($fixture);
        }
    };
}
iterator_checks!(
    "rust-iterators",
    charon_iterator_proof_preserves_source_and_checks_obligations,
    charon_iterator_proof_profile_agrees,
    charon_iterator_proof_expansion_rechecks,
    charon_iterator_proof_audits_checked_frontiers
);
iterator_checks!(
    "rust-iter-references",
    charon_reference_iterator_proof_preserves_source_and_checks_obligations,
    charon_reference_iterator_proof_profile_agrees,
    charon_reference_iterator_proof_expansion_rechecks,
    charon_reference_iterator_proof_audits_checked_frontiers
);
