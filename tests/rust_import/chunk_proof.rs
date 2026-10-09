use super::*;

fn project() -> Project {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("design/charon-trial/chunk-proof");
    let p = Project::new("");
    for (destination, original) in [
        ("chunks.rs", "chunks.rs"),
        ("chunks.ullbc", "chunks.ullbc"),
        ("borrow.click", "chunks.click"),
        ("borrow.click.import.json", "chunks.click.import.json"),
        (
            "borrow.click.import.json.lock",
            "chunks.click.import.json.lock",
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
#[ignore = "nightly: 43 s, over the gate's per-test budget (2026-10-06)"]
fn charon_chunk_proof_preserves_source_and_checks_obligations() {
    assert_eq!(
        include_str!("../../design/charon-trial/chunk-proof/chunks.rs"),
        include_str!("../../examples/rust-chunks-exact/chunks.rs")
    );
    assert_eq!(
        include_str!("../../design/charon-trial/chunk-proof/chunks.click"),
        include_str!("../../examples/rust-chunks-exact/chunks.click")
    );
    let p = project();
    let prepared = load_import(&p.config()).unwrap();
    let proof = fs::read_to_string(p.root.join("borrow.click")).unwrap();
    C0VerificationSession::new_program_prepared(&proof, &prepared).unwrap();
    for invalid in [
        proof.replacen("views bytes[0..bytes.len()];", "", 1),
        proof.replace(
            "ensures result == bytes.len() % 4u64;",
            "ensures result == 4u64;",
        ),
        proof.replace("bytes[k] == old(bytes[k])", "bytes[k] != old(bytes[k])"),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}
#[test]
#[ignore = "nightly: 32 s, over the gate's per-test budget (2026-10-06)"]
fn charon_chunk_proof_tools_agree() {
    let p = project();
    for command in ["verify", "profile"] {
        assert_cli(&p, &[command]);
    }
    let proof = fs::read_to_string(p.root.join("borrow.click")).unwrap();
    let offset = proof.find("execute_until(back_edge())").unwrap();
    let line = proof[..offset].bytes().filter(|&b| b == b'\n').count() + 1;
    let column = offset - proof[..offset].rfind('\n').map_or(0, |p| p + 1) + 1;
    let cursor = format!("{}:{line}:{column}", p.root.join("borrow.click").display());
    assert_cli(&p, &["audit", "--start-at", &cursor, "--max-sites", "1"]);
}
#[test]
#[ignore = "nightly: 46 s, over the gate's per-test budget (2026-10-06)"]
fn charon_chunk_proof_expansion_rechecks() {
    let p = project();
    assert_cli(&p, &["verify"]);
    assert_cli(&p, &["expand", "--claim", "cover.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}
