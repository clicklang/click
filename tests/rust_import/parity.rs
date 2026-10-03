//! Unchanged legacy sources and contracts define migration parity.
use super::*;
use serde::Deserialize;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Entry {
    config: String,
    outcome: String,
    diagnostic: String,
    #[serde(default)]
    migrated_sidecar: Option<String>,
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
        13
    );
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
                if let Some(migrated) = &entry.migrated_sidecar {
                    let sidecar = fs::read_to_string(root.join(migrated)).unwrap();
                    if let Err(error) =
                        C0VerificationSession::new_program_prepared(&sidecar, &prepared)
                    {
                        mismatches.push(format!(
                            "{}: migrated proof failed: {}",
                            entry.config,
                            error.message()
                        ));
                    }
                }
                match C0VerificationSession::new_program_prepared(
                    &fs::read_to_string(sidecar).unwrap(),
                    &prepared,
                ) {
                    Ok(_) => ("verified", String::new()),
                    Err(error) => ("proof-gap", error.message().to_owned()),
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
