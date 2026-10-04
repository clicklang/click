use super::*;

fn project() -> Project {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("design/charon-trial/iterator-proof/rust-iterators");
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
#[test]
fn charon_iterator_proof_preserves_source_and_checks_obligations() {
    assert_eq!(
        include_str!("../../design/charon-trial/iterator-proof/rust-iterators/sum.rs"),
        include_str!("../../examples/rust-iterators/sum.rs")
    );
    assert_eq!(
        include_str!("../../design/charon-trial/iterator-proof/rust-iterators/frozen.click"),
        include_str!("../../examples/rust-iterators/sum.click")
    );
    let p = project();
    let prepared = load_import(&p.config()).unwrap();
    let proof = fs::read_to_string(p.root.join("borrow.click")).unwrap();
    assert!(!proof.contains("__rust_"));
    assert!(!proof.contains("statement("));
    C0VerificationSession::new_program_prepared(&proof, &prepared).unwrap();
    for invalid in [
        proof.replacen("views bytes[0..(int32)(uint32)bytes_len];", "", 1),
        proof.replacen(
            "ensures to_integer(result) == old(prefix(bytes, (int32)(uint32)bytes_len));",
            "ensures to_integer(result) == old(prefix(bytes, (int32)(uint32)bytes_len)) + 1;",
            1,
        ),
        proof.replace("decreases iter_remaining;", "decreases -iter_remaining;"),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}
#[test]
fn charon_iterator_proof_profile_agrees() {
    let p = project();
    assert_cli(&p, &["verify"]);
    assert_cli(&p, &["profile"]);
}
#[test]
fn charon_iterator_proof_expansion_rechecks() {
    let p = project();
    assert_cli(&p, &["verify"]);
    assert_cli(&p, &["expand", "--claim", "sum.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}
#[test]
fn charon_iterator_proof_audits_checked_frontiers() {
    for selector in [
        "execute_until(read(0))",
        "execute_until(assignment(total, 1))",
        "execute_until(back_edge())",
    ] {
        let p = project();
        assert_cli(&p, &["verify"]);
        let proof = fs::read_to_string(p.root.join("borrow.click")).unwrap();
        let offset = proof.find(selector).unwrap();
        let line = proof[..offset].bytes().filter(|&b| b == b'\n').count() + 1;
        let column = offset - proof[..offset].rfind('\n').map_or(0, |p| p + 1) + 1;
        let cursor = format!("{}:{line}:{column}", p.root.join("borrow.click").display());
        assert_cli(&p, &["audit", "--start-at", &cursor, "--max-sites", "1"]);
    }
}
