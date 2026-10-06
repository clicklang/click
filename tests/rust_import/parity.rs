//! Unchanged legacy sources and contracts define migration parity.
use super::*;
use serde::Deserialize;
use sha2::{Digest, Sha256};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Entry {
    config: String,
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
#[test]
fn charon_parity_inventory_covers_every_rust_example() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut actual = Vec::new();
    for directory in fs::read_dir(root.join("examples")).unwrap() {
        let directory = directory.unwrap().path();
        if !directory.is_dir() {
            continue;
        }
        for file in fs::read_dir(directory).unwrap() {
            let path = file.unwrap().path();
            if !path.to_string_lossy().ends_with(".click.import.json") {
                continue;
            }
            let config: serde_json::Value =
                serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
            if config["language"] == "rust" {
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
            let canonical = root.join(entry.config.trim_end_matches(".import.json"));
            let port = root.join(entry.migrated_sidecar.as_ref().unwrap());
            assert_eq!(fs::read(canonical).unwrap(), fs::read(port).unwrap());
        }
    }
    let expected: Vec<_> = entries.into_iter().map(|e| e.config).collect();
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
                .map(|path| (e.config.as_str(), path.as_str()))
        })
        .collect();
    assert_eq!(
        migrated,
        [
            (
                "examples/rust-byte-sum/sum.click.import.json",
                "design/charon-trial/loop-headers/sum-proof.click"
            ),
            (
                "examples/rust-chunks-exact/chunks.click.import.json",
                "design/charon-trial/chunk-proof/chunks.click"
            ),
            (
                "examples/rust-iter-references/sum.click.import.json",
                "design/charon-trial/iterator-proof/rust-iter-references/sum.click"
            ),
            (
                "examples/rust-iterators/sum.click.import.json",
                "design/charon-trial/iterator-proof/rust-iterators/sum.click"
            ),
            (
                "examples/rust-loops/loops.click.import.json",
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
        let path = root.join(&entry.config);
        let config: serde_json::Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        assert_eq!(config["schema"], 3);
        assert!(config.get("backend").is_none());
        assert!(config["artifact"].as_str().unwrap().ends_with(".ullbc"));
        let prepared = load_import(&path).unwrap();
        let sidecar = path.with_file_name(
            path.file_name()
                .unwrap()
                .to_str()
                .unwrap()
                .trim_end_matches(".import.json"),
        );
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
fn charon_canonical_basic_tools_agree() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/basic-rust");
    let p = Project::new("");
    for name in [
        "borrow.rs",
        "borrow.click",
        "borrow.ullbc",
        "borrow.click.import.json",
        "borrow.click.import.json.lock",
    ] {
        fs::write(p.root.join(name), fs::read(root.join(name)).unwrap()).unwrap();
    }
    assert_cli(&p, &["verify"]);
    assert_cli(&p, &["profile"]);
    let prepared = load_import(&p.config()).unwrap();
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
        let original = root.join(&entry.config);
        let directory = original.parent().unwrap();
        let mut config: serde_json::Value =
            serde_json::from_slice(&fs::read(&original).unwrap()).unwrap();
        let source = config["source"].as_str().unwrap().to_owned();
        let p = Project::new("");
        fs::write(
            p.root.join(&source),
            fs::read(directory.join(&source)).unwrap(),
        )
        .unwrap();
        config["schema"] = serde_json::json!(3);
        config["backend"] = serde_json::json!("charon-trial");
        config["exporter"] = serde_json::json!(root.join("target/charon/debug/charon"));
        config["artifact"] = serde_json::json!("parity.ullbc");
        fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
        let (outcome, diagnostic) = match refresh_import(&p.config()) {
            Err(error) => ("rejected", error),
            Ok(()) => {
                let prepared = load_import(&p.config()).unwrap();
                let sidecar = original.with_file_name(
                    original
                        .file_name()
                        .unwrap()
                        .to_string_lossy()
                        .trim_end_matches(".import.json"),
                );
                let canonical = fs::read_to_string(&sidecar).unwrap();
                let canonical_error =
                    C0VerificationSession::new_program_prepared(&canonical, &prepared)
                        .err()
                        .map(|error| error.message().to_owned());
                if let Some(error) = &canonical_error {
                    mismatches.push(format!("{}: canonical proof failed: {error}", entry.config));
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
            mismatches.push(format!("{}: {outcome}: {diagnostic}", entry.config));
        }
    }
    assert!(
        mismatches.is_empty(),
        "parity outcomes changed:\n{}",
        mismatches.join("\n")
    );
}
