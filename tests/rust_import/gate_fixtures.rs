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
        assert_eq!(
            fs::read(p.root.join("borrow.ullbc")).unwrap(),
            artifact,
            "{name}"
        );
    }
}
