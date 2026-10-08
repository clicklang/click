//! Proof regressions consume locked native artifacts. Compiler re-extraction
//! has a separate nightly check and never silently substitutes for a fixture.
use super::*;

pub(super) fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("design/charon-trial/gate-fixtures")
}

pub(super) fn project(name: &str, source: &str) -> Project {
    let fixture = root().join(name);
    assert_eq!(
        fs::read_to_string(fixture.join("borrow.rs")).unwrap(),
        source,
        "the frozen fixture must match the unchanged test input"
    );
    let p = Project::isolated(source);
    for name in [
        "borrow.click.import.json",
        "borrow.click.import.json.lock",
        "borrow.ullbc",
    ] {
        fs::copy(fixture.join(name), p.root.join(name)).unwrap();
    }
    p
}

// Charon retains the compiler input's absolute path. Relocation changes that
// one metadata value; no function, type, span position, or compiler option is
// removed from the comparison.
fn relocated_artifact(bytes: &[u8], source_suffix: &std::path::Path) -> serde_json::Value {
    let mut artifact: serde_json::Value = serde_json::from_slice(bytes).unwrap();
    let files = artifact["data"]["translated"]["files"]
        .as_array_mut()
        .unwrap();
    let mut relocated = 0;
    for file in files {
        if file["name"]["Local"]
            .as_str()
            .is_some_and(|name| std::path::Path::new(name).ends_with(source_suffix))
        {
            file["name"]["Local"] = "borrow.rs".into();
            relocated += 1;
        }
    }
    assert_eq!(relocated, 1, "expected exactly one matching source file");
    artifact
}

#[test]
#[ignore = "nightly: re-extract every frozen Rust gate fixture with the pinned compiler"]
fn frozen_gate_fixtures_match_live_charon_extraction() {
    let mut fixtures: Vec<_> = fs::read_dir(root())
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.is_dir())
        .collect();
    fixtures.sort();
    assert_eq!(fixtures.len(), 12);
    for fixture in fixtures {
        let name = fixture.file_name().unwrap().to_str().unwrap();
        let source = fs::read_to_string(fixture.join("borrow.rs")).unwrap();
        let p = project(name, &source);
        load_import(&p.config()).unwrap();
        let artifact = fs::read(p.root.join("borrow.ullbc")).unwrap();
        let mut config: serde_json::Value =
            serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
        config["exporter"] = std::env::var("CLICK_CHARON").unwrap().into();
        fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
        refresh_import(&p.config()).unwrap();
        load_import(&p.config()).unwrap();
        let frozen_suffix = PathBuf::from("design/charon-trial/gate-fixtures")
            .join(name)
            .join("borrow.rs");
        let expected = relocated_artifact(&artifact, &frozen_suffix);
        let actual = relocated_artifact(
            &fs::read(p.root.join("borrow.ullbc")).unwrap(),
            &p.root.join("borrow.rs"),
        );
        assert!(
            actual == expected,
            "{name}: native artifact changed after source-path relocation"
        );
    }
}
