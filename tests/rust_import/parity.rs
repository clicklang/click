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
    /// The digest of the archive's bytes before its one-time respelling to
    /// today's syntax (git history holds those bytes).
    #[serde(default)]
    original_sha256: Option<String>,
}
fn inventory() -> Vec<Entry> {
    serde_json::from_str(include_str!("../../design/charon-trial/parity.json")).unwrap()
}

/// Each archived sidecar is pinned by digest and reads in today's syntax.
/// The archives were respelled once (2026-10-26) from their original bytes,
/// whose digests `original_sha256` records: tactic names, Rust signatures,
/// `as` casts and qualified library citations. Each respelled file is
/// byte-identical to what the retired reading adapter produced from the
/// original, so its contracts, specification functions and proofs, gaps
/// included, are the original's. The live parity sweep still checks each
/// archive's recorded outcome.
#[test]
fn charon_frozen_sidecars_are_pinned_and_parse() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for entry in inventory()
        .iter()
        .filter(|entry| entry.frozen_sidecar.is_some())
    {
        let frozen = entry.frozen_sidecar.as_ref().unwrap();
        let source = fs::read_to_string(root.join(frozen)).unwrap();
        assert_eq!(
            format!("{:x}", Sha256::digest(source.as_bytes())),
            entry.frozen_sha256.as_deref().unwrap(),
            "{frozen}"
        );
        assert_ne!(entry.original_sha256, entry.frozen_sha256, "{frozen}");
        click::surface::parse(&source).unwrap();
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
        assert_eq!(
            entry.original_sha256.is_some(),
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
        13
    );
    assert_eq!(
        entries
            .iter()
            .filter(|e| e.outcome == "verified" || e.migrated_sidecar.is_some())
            .count(),
        18
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
        adopted, 17,
        "canonical adoption uses the fixed 17-fixture baseline"
    );
}

#[cfg(not(feature = "fast-gate"))]
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
                        &fs::read_to_string(root.join(frozen)).unwrap(),
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
