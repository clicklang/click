//! Unchanged legacy sources and contracts define migration parity.
use super::*;
use serde::Deserialize;
use sha2::{Digest, Sha256};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Entry {
    sidecar: String,
    outcome: String,
    diagnostic: String,
    #[serde(default)]
    migrated_sidecar: Option<String>,
    #[serde(default)]
    frozen_sidecar: Option<String>,
    #[serde(default)]
    frozen_sha256: Option<String>,
}
fn inventory() -> Vec<Entry> {
    serde_json::from_str(include_str!("../../design/charon-trial/parity.json")).unwrap()
}

/// Read hash-pinned historical proofs through today's signature and tactic spelling.
/// This is a fixture adapter, not a production compatibility mode. The files
/// and their proof scripts stay unchanged, including their original proof gaps.
pub(super) fn frozen_proof_input(source: &str) -> String {
    let hash = format!("{:x}", Sha256::digest(source.as_bytes()));
    assert!(
        inventory()
            .iter()
            .any(|entry| entry.frozen_sha256.as_deref() == Some(hash.as_str())),
        "only a hash-pinned historical fixture may use this adapter"
    );
    let mut input = source.replace("close_invariants by", "close_invariants() by");
    for (old, current) in [
        (
            "int32 sum(const uint8* bytes, uint64 bytes_len)",
            "fn sum(bytes: &[u8]) -> i32",
        ),
        (
            "uint64 cover(const uint8* bytes, uint64 bytes_len)",
            "fn cover(bytes: &[u8]) -> usize",
        ),
        ("int32 count(int32 n)", "fn count(n: i32) -> i32"),
        (
            "int32 accumulate(int32 n, int32 value)",
            "fn accumulate(n: i32, value: i32) -> i32",
        ),
        (
            "uint64 walk(const uint8* bytes, uint64 bytes_len)",
            "fn walk(bytes: &[u8]) -> usize",
        ),
    ] {
        input = input.replace(old, current);
    }
    input.replace("bytes_len", "bytes.len()") + FROZEN_LIBRARY_IMPORTS
}

/// The pinned files predate Click library imports. Their proofs cite
/// `click::integer` and `click::machine_integer` theorems; the imports go
/// last so every pinned line keeps its position.
const FROZEN_LIBRARY_IMPORTS: &str = "\nimport click::integer;\nimport click::machine_integer;\n";

#[test]
fn charon_frozen_proof_adapter_preserves_the_contracts_and_pinned_bytes() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for entry in inventory()
        .iter()
        .filter(|entry| entry.frozen_sidecar.is_some())
    {
        let source = fs::read_to_string(root.join(entry.frozen_sidecar.as_ref().unwrap())).unwrap();
        let input = frozen_proof_input(&source);
        // Keep the original C signatures and update the shared tactic spelling
        // on both sides. The parsed contracts must still agree.
        let c_input = source
            .replace(".rs\"", ".c\"")
            .replace("close_invariants by", "close_invariants() by")
            + FROZEN_LIBRARY_IMPORTS;
        assert_eq!(
            click::surface::parse(&input).unwrap().function_blocks(),
            click::surface::parse(&c_input).unwrap().function_blocks(),
            "{}",
            entry.frozen_sidecar.as_ref().unwrap()
        );
        assert_eq!(
            format!("{:x}", Sha256::digest(source.as_bytes())),
            entry.frozen_sha256.as_deref().unwrap()
        );
    }
}
#[test]
fn charon_parity_inventory_covers_every_rust_example() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut actual = Vec::new();
    for directory in fs::read_dir(root.join("examples")).unwrap() {
        let directory = directory.unwrap().path();
        if !directory.is_dir() {
            continue;
        }
        if !directory.join("click.project.json").exists() {
            continue;
        }
        for file in fs::read_dir(directory).unwrap() {
            let path = file.unwrap().path();
            if path
                .extension()
                .is_none_or(|extension| extension != "click")
            {
                continue;
            }
            let source = fs::read_to_string(&path).unwrap();
            if source
                .lines()
                .any(|line| line.starts_with("verifying ") && line.contains(".rs\""))
            {
                actual.push(
                    path.strip_prefix(&root)
                        .unwrap()
                        .to_string_lossy()
                        .into_owned(),
                );
            }
        }
    }
    actual.sort();
    let entries = inventory();
    for entry in &entries {
        assert!(matches!(
            entry.outcome.as_str(),
            "verified" | "rejected" | "proof-gap"
        ));
        assert_eq!(entry.diagnostic.is_empty(), entry.outcome == "verified");
        assert_eq!(
            entry.frozen_sidecar.is_some(),
            entry.migrated_sidecar.is_some()
        );
        assert_eq!(
            entry.frozen_sha256.is_some(),
            entry.frozen_sidecar.is_some()
        );
        if let Some(frozen) = &entry.frozen_sidecar {
            let bytes = fs::read(root.join(frozen)).unwrap();
            assert_eq!(
                Some(format!("{:x}", Sha256::digest(&bytes))),
                entry.frozen_sha256
            );
            let canonical = root.join(&entry.sidecar);
            let port = root.join(entry.migrated_sidecar.as_ref().unwrap());
            assert_eq!(fs::read(canonical).unwrap(), fs::read(port).unwrap());
        }
    }
    let expected: Vec<_> = entries.into_iter().map(|e| e.sidecar).collect();
    assert_eq!(
        actual, expected,
        "update the live parity inventory when fixtures change"
    );
}
#[test]
fn charon_parity_migrated_proof_inventory_is_explicit() {
    let entries = inventory();
    let migrated: Vec<_> = entries
        .iter()
        .filter_map(|e| {
            e.migrated_sidecar
                .as_ref()
                .map(|path| (e.sidecar.as_str(), path.as_str()))
        })
        .collect();
    assert_eq!(
        migrated,
        [
            (
                "examples/rust-byte-sum/sum.click",
                "design/charon-trial/loop-headers/sum-proof.click"
            ),
            (
                "examples/rust-chunks-exact/chunks.click",
                "design/charon-trial/chunk-proof/chunks.click"
            ),
            (
                "examples/rust-iter-references/sum.click",
                "design/charon-trial/iterator-proof/rust-iter-references/sum.click"
            ),
            (
                "examples/rust-iterators/sum.click",
                "design/charon-trial/iterator-proof/rust-iterators/sum.click"
            ),
            (
                "examples/rust-loops/loops.click",
                "design/charon-trial/loop-headers/loops-assignments.click"
            ),
        ]
    );
    assert_eq!(
        entries.iter().filter(|e| e.outcome == "verified").count(),
        11
    );
    assert_eq!(
        entries
            .iter()
            .filter(|e| e.outcome == "verified" || e.migrated_sidecar.is_some())
            .count(),
        16
    );
}

/// Canonical examples use locked native imports without starting either compiler.
#[test]
#[ignore = "nightly: 35 s, over the gate's per-test budget (2026-10-06)"]
fn charon_canonical_examples_use_locked_native_artifacts() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut adopted = 0;
    for entry in inventory() {
        let sidecar = root.join(&entry.sidecar);
        let prepared = prepared_sidecar(&sidecar).unwrap();
        C0VerificationSession::new_program_prepared(
            &fs::read_to_string(sidecar).unwrap(),
            &prepared,
        )
        .unwrap();
        adopted += 1;
    }
    assert_eq!(
        adopted, 16,
        "canonical adoption uses the fixed 16-fixture baseline"
    );
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn charon_canonical_basic_tools_agree() {
    let p = Project::from_fixture("examples/basic-rust");
    assert_cli(&p, &["verify"]);
    assert_cli(&p, &["profile"]);
    let prepared = p.prepared().unwrap();
    let expanded =
        click::surface::expand_program_prepared_tactic_source_at(SIDECAR, &prepared, 8, 5).unwrap();
    C0VerificationSession::new_program_prepared(&expanded, &prepared).unwrap();
    assert_cli(
        &p,
        &[
            "audit",
            "--claim",
            "choose.contract",
            "--start-at",
            &format!("{}:8:5", p.root.join("borrow.click").display()),
            "--max-sites",
            "1",
        ],
    );
    assert_cli(&p, &["expand", "--claim", "choose.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
    assert_cli(&p, &["expand", "--claim", "update.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
    assert_cli(&p, &["audit", "--max-sites", "1"]);
}

#[test]
#[ignore = "requires the pinned live Charon/compiler; scripts/check.sh --charon-live"]
fn charon_legacy_parity_live_refresh_and_unchanged_contracts() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut mismatches = Vec::new();
    for entry in inventory() {
        let original = root.join(&entry.sidecar);
        let p = Project::from_fixture(
            original
                .parent()
                .unwrap()
                .strip_prefix(&root)
                .unwrap()
                .to_str()
                .unwrap(),
        );
        let sidecar = p.root.join(original.file_name().unwrap());
        let (outcome, diagnostic) = match p.refresh() {
            Err(error) => ("rejected", error),
            Ok(()) => {
                let prepared = prepared_sidecar(&sidecar).unwrap();
                let canonical = fs::read_to_string(&sidecar).unwrap();
                let canonical_error =
                    C0VerificationSession::new_program_prepared(&canonical, &prepared)
                        .err()
                        .map(|error| error.message().to_owned());
                if let Some(error) = &canonical_error {
                    mismatches.push(format!(
                        "{}: canonical proof failed: {error}",
                        entry.sidecar
                    ));
                }
                // Preserve original frozen outcomes independently of canonical adoption.
                let frozen_error = if let Some(frozen) = &entry.frozen_sidecar {
                    C0VerificationSession::new_program_prepared(
                        &frozen_proof_input(&fs::read_to_string(root.join(frozen)).unwrap()),
                        &prepared,
                    )
                    .err()
                    .map(|error| error.message().to_owned())
                } else {
                    canonical_error
                };
                match frozen_error {
                    None => ("verified", String::new()),
                    Some(error) => ("proof-gap", error),
                }
            }
        };
        if outcome != entry.outcome || !diagnostic.contains(&entry.diagnostic) {
            mismatches.push(format!("{}: {outcome}: {diagnostic}", entry.sidecar));
        }
    }
    assert!(
        mismatches.is_empty(),
        "parity outcomes changed:\n{}",
        mismatches.join("\n")
    );
}
